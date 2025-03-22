@Library('Shared') _
pipeline {
    agent { label 'Node' }
    
    environment {
        SONAR_HOME = tool "Sonar"
    }
    
    parameters {
        string(name: 'FRONTEND_DOCKER_TAG', defaultValue: '', description: 'Docker tag for frontend image')
        string(name: 'BACKEND_DOCKER_TAG', defaultValue: '', description: 'Docker tag for backend image')
    }
    
    stages {
        stage("Validate Parameters") {
            steps {
                script {
                    if (!params.FRONTEND_DOCKER_TAG?.trim() || !params.BACKEND_DOCKER_TAG?.trim()) {
                        error("Both FRONTEND_DOCKER_TAG and BACKEND_DOCKER_TAG must be provided.")
                    }
                    echo "Parameters validated: FRONTEND_DOCKER_TAG=${params.FRONTEND_DOCKER_TAG}, BACKEND_DOCKER_TAG=${params.BACKEND_DOCKER_TAG}"
                }
            }
        }

        stage("Cleanup Workspace") {
            steps {
                cleanWs()
                echo "Workspace cleaned successfully."
            }
        }

        stage('Git: Checkout Code') {
            steps {
                script {
                    echo "Checking out source code..."
                    code_checkout("https://github.com/LondheShubham153/Wanderlust-Mega-Project.git", "main")
                }
            }
        }

        stage("Security Scans") {
            parallel {
                stage("Trivy: Filesystem Scan") {
                    steps {
                        script {
                            echo "Running Trivy scan..."
                            trivy_scan()
                        }
                    }
                }

                stage("OWASP: Dependency Check") {
                    steps {
                        script {
                            echo "Running OWASP Dependency Check..."
                            owasp_dependency()
                        }
                    }
                }
            }
        }

        stage("SonarQube: Code Analysis") {
            steps {
                script {
                    echo "Starting SonarQube analysis..."
                    sonarqube_analysis("Sonar", "wanderlust", "wanderlust")
                }
            }
        }

        stage("SonarQube: Quality Gate Check") {
            steps {
                script {
                    echo "Checking SonarQube Quality Gates..."
                    sonarqube_code_quality()
                }
            }
        }

        stage("Setup Environment Variables") {
            parallel {
                stage("Backend Setup") {
                    steps {
                        script {
                            dir("Automations") {
                                sh "bash updatebackendnew.sh"
                                echo "Backend environment updated."
                            }
                        }
                    }
                }

                stage("Frontend Setup") {
                    steps {
                        script {
                            dir("Automations") {
                                sh "bash updatefrontendnew.sh"
                                echo "Frontend environment updated."
                            }
                        }
                    }
                }
            }
        }

        stage("Docker: Build and Push Images") {
            steps {
                script {
                    try {
                        echo "Building and pushing backend image..."
                        dir('backend') {
                            docker_build("wanderlust-backend-beta", params.BACKEND_DOCKER_TAG, "trainwithshubham")
                            docker_push("wanderlust-backend-beta", params.BACKEND_DOCKER_TAG, "trainwithshubham")
                        }

                        echo "Building and pushing frontend image..."
                        dir('frontend') {
                            docker_build("wanderlust-frontend-beta", params.FRONTEND_DOCKER_TAG, "trainwithshubham")
                            docker_push("wanderlust-frontend-beta", params.FRONTEND_DOCKER_TAG, "trainwithshubham")
                        }

                        echo "Docker images built and pushed successfully."
                    } catch (Exception e) {
                        error "Docker build or push failed: ${e.message}"
                    }
                }
            }
        }
    }

    post {
        success {
            echo "Pipeline execution successful. Archiving artifacts..."
            archiveArtifacts artifacts: '*.xml', followSymlinks: false

            echo "Triggering Wanderlust-CD pipeline..."
            build job: "Wanderlust-CD", parameters: [
                string(name: 'FRONTEND_DOCKER_TAG', value: params.FRONTEND_DOCKER_TAG),
                string(name: 'BACKEND_DOCKER_TAG', value: params.BACKEND_DOCKER_TAG)
            ]
        }

        failure {
            echo "Pipeline execution failed. Check logs for details."
        }
    }
}
